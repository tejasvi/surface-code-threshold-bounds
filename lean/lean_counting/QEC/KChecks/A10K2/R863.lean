import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3452 = true := by
  decide +kernel

theorem tot3452 : totK PA10K2 A10K2.t3452 = [0, 0, 0, 174236993409, 1057077128034, 1976246932588, 1411286010045, 347290561788, 25734533292, 0] := by
  decide +kernel

theorem rows3453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3453 = true := by
  decide +kernel

theorem tot3453 : totK PA10K2 A10K2.t3453 = [0, 0, 0, 195419158680, 982810478557, 1846783012497, 1336342449418, 237644251183, 6034215561, 0] := by
  decide +kernel

theorem rows3454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3454 = true := by
  decide +kernel

theorem tot3454 : totK PA10K2 A10K2.t3454 = [0, 0, 0, 465142732817, 1682035084263, 1882520866885, 567887525362, 37254374173, 0, 0] := by
  decide +kernel

theorem rows3455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3455 = true := by
  decide +kernel

theorem tot3455 : totK PA10K2 A10K2.t3455 = [0, 0, 0, 112111361307, 1207734620452, 2228637631981, 935620809672, 63088128279, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
