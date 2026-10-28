import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6904 = true := by
  decide +kernel

theorem tot6904 : totK PD2M8K2 D2M8K2.t6904 = [0, 124690721972, 423476186714, 328368097782, 32442212991, 0, 0, 0] := by
  decide +kernel

theorem rows6905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6905 = true := by
  decide +kernel

theorem tot6905 : totK PD2M8K2 D2M8K2.t6905 = [0, 183524717629, 437749376873, 249643361545, 26841706846, 0, 0, 0] := by
  decide +kernel

theorem rows6906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6906 = true := by
  decide +kernel

theorem tot6906 : totK PD2M8K2 D2M8K2.t6906 = [0, 106069037658, 420054032328, 336573011793, 30558203185, 0, 0, 0] := by
  decide +kernel

theorem rows6907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6907 = true := by
  decide +kernel

theorem tot6907 : totK PD2M8K2 D2M8K2.t6907 = [0, 0, 218382874805, 497299391617, 162618301602, 5172807878, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
