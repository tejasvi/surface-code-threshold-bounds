import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13420 = true := by
  decide +kernel

theorem tot13420 : totK PD2M8K2 D2M8K2.t13420 = [0, 0, 84596764418, 306707950519, 367615873722, 146659480309, 14724172215, 0] := by
  decide +kernel

theorem rows13421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13421 = true := by
  decide +kernel

theorem tot13421 : totK PD2M8K2 D2M8K2.t13421 = [0, 0, 0, 221579689562, 487527111880, 176614390856, 7994456143, 0] := by
  decide +kernel

theorem rows13422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13422 = true := by
  decide +kernel

theorem tot13422 : totK PD2M8K2 D2M8K2.t13422 = [0, 0, 138437536193, 369124091807, 320477471018, 81893353280, 1409560813, 0] := by
  decide +kernel

theorem rows13423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13423 = true := by
  decide +kernel

theorem tot13423 : totK PD2M8K2 D2M8K2.t13423 = [0, 0, 162116943937, 442330630684, 280183245499, 27256234641, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
