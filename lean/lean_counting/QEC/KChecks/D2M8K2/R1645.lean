import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6580 = true := by
  decide +kernel

theorem tot6580 : totK PD2M8K2 D2M8K2.t6580 = [171162320902, 483129301774, 242118843865, 12435483790, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6581 = true := by
  decide +kernel

theorem tot6581 : totK PD2M8K2 D2M8K2.t6581 = [0, 210884431062, 460182995130, 210716546708, 21383112939, 0, 0, 0] := by
  decide +kernel

theorem rows6582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6582 = true := by
  decide +kernel

theorem tot6582 : totK PD2M8K2 D2M8K2.t6582 = [0, 173792683368, 487247917510, 221194882580, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows6583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6583 = true := by
  decide +kernel

theorem tot6583 : totK PD2M8K2 D2M8K2.t6583 = [134574193550, 350249835610, 279871437812, 123291259577, 8032917247, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
