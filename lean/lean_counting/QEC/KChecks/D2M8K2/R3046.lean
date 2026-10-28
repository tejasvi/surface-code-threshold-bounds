import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12184 = true := by
  decide +kernel

theorem tot12184 : totK PD2M8K2 D2M8K2.t12184 = [86868443710, 320817869442, 379941681413, 107760351001, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows12185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12185 = true := by
  decide +kernel

theorem tot12185 : totK PD2M8K2 D2M8K2.t12185 = [163759732328, 459302855245, 247445160179, 17033427234, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12186 = true := by
  decide +kernel

theorem tot12186 : totK PD2M8K2 D2M8K2.t12186 = [72446816662, 321413128113, 402948784849, 91751935063, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows12187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12187 = true := by
  decide +kernel

theorem tot12187 : totK PD2M8K2 D2M8K2.t12187 = [0, 184190174806, 470941577680, 197290221745, 8669917095, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
