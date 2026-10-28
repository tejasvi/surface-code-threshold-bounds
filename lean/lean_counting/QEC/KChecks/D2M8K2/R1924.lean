import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7696 = true := by
  decide +kernel

theorem tot7696 : totK PD2M8K2 D2M8K2.t7696 = [0, 0, 90277532827, 292263246953, 355648952502, 150275743521, 11568901818, 0] := by
  decide +kernel

theorem rows7697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7697 = true := by
  decide +kernel

theorem tot7697 : totK PD2M8K2 D2M8K2.t7697 = [0, 0, 154037611041, 468778152123, 241992123170, 12063790339, 0, 0] := by
  decide +kernel

theorem rows7698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7698 = true := by
  decide +kernel

theorem tot7698 : totK PD2M8K2 D2M8K2.t7698 = [0, 0, 169789109226, 450267583659, 239162415233, 16914169947, 0, 0] := by
  decide +kernel

theorem rows7699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7699 = true := by
  decide +kernel

theorem tot7699 : totK PD2M8K2 D2M8K2.t7699 = [0, 0, 0, 283049814528, 500793448732, 94811936702, 1334361349, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
