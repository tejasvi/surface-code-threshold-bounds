import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6724 = true := by
  decide +kernel

theorem tot6724 : totK PA10K2 A10K2.t6724 = [0, 269112687947, 1169641102954, 1859565542995, 1173080203210, 200444753646, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows6725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6725 = true := by
  decide +kernel

theorem tot6725 : totK PA10K2 A10K2.t6725 = [0, 315274092787, 1569360341545, 2113928096709, 682722493198, 38902754494, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6726 = true := by
  decide +kernel

theorem tot6726 : totK PA10K2 A10K2.t6726 = [0, 190107525503, 1065037144179, 2008727241485, 1267273725333, 202883465764, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows6727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6727 = true := by
  decide +kernel

theorem tot6727 : totK PA10K2 A10K2.t6727 = [0, 611775513763, 2012676159907, 1889416967815, 484259277740, 25852139541, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
