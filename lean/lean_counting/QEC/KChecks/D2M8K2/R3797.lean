import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15188 = true := by
  decide +kernel

theorem tot15188 : totK PD2M8K2 D2M8K2.t15188 = [0, 0, 209403792092, 489198800504, 187658555346, 7689860642, 0, 0] := by
  decide +kernel

theorem rows15189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15189 = true := by
  decide +kernel

theorem tot15189 : totK PD2M8K2 D2M8K2.t15189 = [0, 0, 171587095951, 484035673741, 216341676765, 8512448457, 0, 0] := by
  decide +kernel

theorem rows15190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15190 = true := by
  decide +kernel

theorem tot15190 : totK PD2M8K2 D2M8K2.t15190 = [0, 0, 177468590838, 472954617556, 216369641038, 11968863130, 0, 0] := by
  decide +kernel

theorem rows15191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15191 = true := by
  decide +kernel

theorem tot15191 : totK PD2M8K2 D2M8K2.t15191 = [0, 194625098643, 470979962829, 202720992168, 25190158638, 2818680842, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
