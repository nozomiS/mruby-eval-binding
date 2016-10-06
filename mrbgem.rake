MRuby::Gem::Specification.new('mruby-eval-binding') do |spec|
  spec.license = 'MIT'
  spec.authors = 'mruby developers', 'Nozomi SATO'
  spec.summary = 'standard Kernel#eval method and class Binding'

  add_dependency 'mruby-compiler', :core => 'mruby-compiler'
end
