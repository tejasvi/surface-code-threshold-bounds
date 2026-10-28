import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3656 = true := by
  decide +kernel

theorem tot3656 : totK PA10K2 A10K2.t3656 = [0, 0, 0, 163519178053, 1083030093903, 1942630484912, 1148206610581, 199688222784, 5453062850, 0] := by
  decide +kernel

theorem rows3657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3657 = true := by
  decide +kernel

theorem tot3657 : totK PA10K2 A10K2.t3657 = [0, 0, 0, 573671905811, 1868632169767, 1747972573314, 475035237426, 31821298896, 0, 0] := by
  decide +kernel

theorem rows3658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3658 = true := by
  decide +kernel

theorem tot3658 : totK PA10K2 A10K2.t3658 = [0, 0, 0, 0, 965153760178, 2410839117394, 1107276363809, 84064502827, 0, 0] := by
  decide +kernel

theorem rows3659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3659 = true := by
  decide +kernel

theorem tot3659 : totK PA10K2 A10K2.t3659 = [0, 0, 0, 630339857083, 1901151340150, 1671507597330, 660255832863, 136147139169, 5685526223, 0] := by
  decide +kernel

end QECKChecks.A10K2
