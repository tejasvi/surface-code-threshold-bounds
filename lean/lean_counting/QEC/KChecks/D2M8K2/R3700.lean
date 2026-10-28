import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14800 = true := by
  decide +kernel

theorem tot14800 : totK PD2M8K2 D2M8K2.t14800 = [0, 81621031138, 424613451558, 368866032015, 42403421976, 0, 0, 0] := by
  decide +kernel

theorem rows14801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14801 = true := by
  decide +kernel

theorem tot14801 : totK PD2M8K2 D2M8K2.t14801 = [0, 0, 224221832250, 502643049299, 153322033337, 2484078857, 0, 0] := by
  decide +kernel

theorem rows14802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14802 = true := by
  decide +kernel

theorem tot14802 : totK PD2M8K2 D2M8K2.t14802 = [178250561612, 388425051226, 132194273625, 95632644421, 90042241549, 6818291842, 0, 0] := by
  decide +kernel

theorem rows14803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14803 = true := by
  decide +kernel

theorem tot14803 : totK PD2M8K2 D2M8K2.t14803 = [159735099624, 433405997785, 249247518466, 19672244160, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
