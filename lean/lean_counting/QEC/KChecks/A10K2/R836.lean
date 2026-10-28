import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3344 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3344 = true := by
  decide +kernel

theorem tot3344 : totK PA10K2 A10K2.t3344 = [0, 61604139585, 576326131619, 1807355144271, 1906554085442, 518991473134, 31677228370, 0, 0, 0] := by
  decide +kernel

theorem rows3345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3345 = true := by
  decide +kernel

theorem tot3345 : totK PA10K2 A10K2.t3345 = [0, 481333235783, 1785729363699, 1938788849155, 584417521546, 40918548881, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3346 = true := by
  decide +kernel

theorem tot3346 : totK PA10K2 A10K2.t3346 = [0, 330865856800, 1556848122879, 2171899838638, 863337033674, 67762206670, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3347 = true := by
  decide +kernel

theorem tot3347 : totK PA10K2 A10K2.t3347 = [0, 0, 490628743117, 1974652904043, 2052041030961, 469269354653, 13816090359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
