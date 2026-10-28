import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4168 = true := by
  decide +kernel

theorem tot4168 : totK PD2M8K2 D2M8K2.t4168 = [0, 160152142738, 444138693992, 282411565433, 30303715720, 0, 0, 0] := by
  decide +kernel

theorem rows4169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4169 = true := by
  decide +kernel

theorem tot4169 : totK PD2M8K2 D2M8K2.t4169 = [0, 104104058892, 401153106344, 339274071145, 50104601382, 1164319620, 0, 0] := by
  decide +kernel

theorem rows4170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4170 = true := by
  decide +kernel

theorem tot4170 : totK PD2M8K2 D2M8K2.t4170 = [0, 0, 231539533206, 496822456985, 162930688695, 8199387738, 0, 0] := by
  decide +kernel

theorem rows4171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4171 = true := by
  decide +kernel

theorem tot4171 : totK PD2M8K2 D2M8K2.t4171 = [0, 130141355245, 366156003476, 318405260555, 79899178192, 2251664545, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
