import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14756 = true := by
  decide +kernel

theorem tot14756 : totK PD2M8K2 D2M8K2.t14756 = [0, 203575498578, 482332784818, 214160926438, 10309306163, 0, 0, 0] := by
  decide +kernel

theorem rows14757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14757 = true := by
  decide +kernel

theorem tot14757 : totK PD2M8K2 D2M8K2.t14757 = [0, 184286421408, 465707121214, 213867172713, 12319708528, 0, 0, 0] := by
  decide +kernel

theorem rows14758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14758 = true := by
  decide +kernel

theorem tot14758 : totK PD2M8K2 D2M8K2.t14758 = [0, 186507107262, 481136688963, 213893928259, 10178307621, 0, 0, 0] := by
  decide +kernel

theorem rows14759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14759 = true := by
  decide +kernel

theorem tot14759 : totK PD2M8K2 D2M8K2.t14759 = [0, 152446736486, 448119591784, 242462210209, 17940980630, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
