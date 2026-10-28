import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7968 = true := by
  decide +kernel

theorem tot7968 : totK PD2M8K2 D2M8K2.t7968 = [0, 0, 0, 204545527234, 476333808313, 167680292319, 9396886405, 0] := by
  decide +kernel

theorem rows7969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7969 = true := by
  decide +kernel

theorem tot7969 : totK PD2M8K2 D2M8K2.t7969 = [0, 0, 0, 222101764654, 495178375806, 159166957673, 5265834820, 0] := by
  decide +kernel

theorem rows7970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7970 = true := by
  decide +kernel

theorem tot7970 : totK PD2M8K2 D2M8K2.t7970 = [0, 0, 138584818715, 413996467638, 348547199269, 37781393629, 0, 0] := by
  decide +kernel

theorem rows7971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7971 = true := by
  decide +kernel

theorem tot7971 : totK PD2M8K2 D2M8K2.t7971 = [0, 0, 195187085752, 469217205710, 231136081062, 13691613702, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
