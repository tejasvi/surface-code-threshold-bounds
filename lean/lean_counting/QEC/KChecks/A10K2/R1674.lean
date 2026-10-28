import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6696 = true := by
  decide +kernel

theorem tot6696 : totK PA10K2 A10K2.t6696 = [0, 115487560146, 756765737287, 1852164341522, 1819219609925, 533685315836, 43911449185, 0, 0, 0] := by
  decide +kernel

theorem rows6697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6697 = true := by
  decide +kernel

theorem tot6697 : totK PA10K2 A10K2.t6697 = [0, 492465457491, 1776550062212, 1923747860093, 533778489045, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6698 = true := by
  decide +kernel

theorem tot6698 : totK PA10K2 A10K2.t6698 = [0, 151425221940, 1020026139371, 1982752701136, 1417946690789, 346820212941, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows6699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6699 = true := by
  decide +kernel

theorem tot6699 : totK PA10K2 A10K2.t6699 = [0, 275973632717, 1183659211906, 1871596913402, 1249697684894, 217358208846, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
