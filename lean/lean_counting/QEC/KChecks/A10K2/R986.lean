import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3944 = true := by
  decide +kernel

theorem tot3944 : totK PA10K2 A10K2.t3944 = [0, 0, 479484978929, 1851550836160, 1915112130772, 507554325259, 32470817489, 0, 0, 0] := by
  decide +kernel

theorem rows3945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3945 = true := by
  decide +kernel

theorem tot3945 : totK PA10K2 A10K2.t3945 = [0, 0, 562153162969, 2000216864932, 1960030771229, 447097975674, 13227942247, 0, 0, 0] := by
  decide +kernel

theorem rows3946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3946 = true := by
  decide +kernel

theorem tot3946 : totK PA10K2 A10K2.t3946 = [0, 0, 552655315378, 1858598308997, 1834678946253, 465287274360, 30953568651, 0, 0, 0] := by
  decide +kernel

theorem rows3947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3947 = true := by
  decide +kernel

theorem tot3947 : totK PA10K2 A10K2.t3947 = [0, 0, 110963681569, 1320586734486, 2309421490188, 860680070808, 64575419044, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
