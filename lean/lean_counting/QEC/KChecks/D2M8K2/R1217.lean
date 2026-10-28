import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4868 = true := by
  decide +kernel

theorem tot4868 : totK PD2M8K2 D2M8K2.t4868 = [0, 0, 202177483556, 485799191743, 208478083672, 12178391273, 0, 0] := by
  decide +kernel

theorem rows4869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4869 = true := by
  decide +kernel

theorem tot4869 : totK PD2M8K2 D2M8K2.t4869 = [0, 0, 0, 304749226666, 478283491793, 80931798590, 1096505104, 0] := by
  decide +kernel

theorem rows4870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4870 = true := by
  decide +kernel

theorem tot4870 : totK PD2M8K2 D2M8K2.t4870 = [0, 0, 81786931619, 308959137786, 393936485708, 103868982534, 3884009855, 0] := by
  decide +kernel

theorem rows4871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4871 = true := by
  decide +kernel

theorem tot4871 : totK PD2M8K2 D2M8K2.t4871 = [0, 0, 154034117758, 453578951617, 273497005578, 23900848461, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
