import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5824 = true := by
  decide +kernel

theorem tot5824 : totK PA10K2 A10K2.t5824 = [0, 0, 112111361307, 1260392119185, 2282483956443, 1001181778865, 73641457032, 0, 0, 0] := by
  decide +kernel

theorem rows5825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5825 = true := by
  decide +kernel

theorem tot5825 : totK PA10K2 A10K2.t5825 = [0, 0, 0, 521506218450, 1895182778872, 1746428079310, 404780947017, 26172145312, 0, 0] := by
  decide +kernel

theorem rows5826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5826 = true := by
  decide +kernel

theorem tot5826 : totK PA10K2 A10K2.t5826 = [0, 0, 0, 583064909076, 1997577732092, 1818716164778, 372615454668, 11740596405, 0, 0] := by
  decide +kernel

theorem rows5827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5827 = true := by
  decide +kernel

theorem tot5827 : totK PA10K2 A10K2.t5827 = [0, 0, 0, 475528897785, 1807367645579, 1955382955820, 525092237180, 32470943963, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
