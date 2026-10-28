import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7108 = true := by
  decide +kernel

theorem tot7108 : totK PD2M8K2 D2M8K2.t7108 = [0, 0, 200078777925, 477943015806, 228136245762, 16104584588, 0, 0] := by
  decide +kernel

theorem rows7109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7109 = true := by
  decide +kernel

theorem tot7109 : totK PD2M8K2 D2M8K2.t7109 = [0, 0, 181429604811, 477944278921, 221006840789, 12183533023, 0, 0] := by
  decide +kernel

theorem rows7110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7110 = true := by
  decide +kernel

theorem tot7110 : totK PD2M8K2 D2M8K2.t7110 = [0, 0, 0, 301206690659, 477733110474, 95090055430, 1162935789, 0] := by
  decide +kernel

theorem rows7111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7111 = true := by
  decide +kernel

theorem tot7111 : totK PD2M8K2 D2M8K2.t7111 = [0, 0, 0, 205322036553, 450699293722, 181127221267, 11853261585, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
