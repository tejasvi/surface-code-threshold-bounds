import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14816 = true := by
  decide +kernel

theorem tot14816 : totK PD2M8K2 D2M8K2.t14816 = [71991942624, 350851793806, 380031076265, 70847918370, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows14817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14817 = true := by
  decide +kernel

theorem tot14817 : totK PD2M8K2 D2M8K2.t14817 = [53178690646, 295274262847, 433072887129, 114075475192, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows14818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14818 = true := by
  decide +kernel

theorem tot14818 : totK PD2M8K2 D2M8K2.t14818 = [179646333992, 459245205673, 254702509529, 23050312993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14819 = true := by
  decide +kernel

theorem tot14819 : totK PD2M8K2 D2M8K2.t14819 = [191929596574, 481982748558, 228789780962, 14326083334, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
