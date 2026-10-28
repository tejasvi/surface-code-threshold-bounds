import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14052 = true := by
  decide +kernel

theorem tot14052 : totK PD2M8K2 D2M8K2.t14052 = [0, 0, 0, 275098159090, 477798334205, 122861218238, 4164527997, 0] := by
  decide +kernel

theorem rows14053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14053 = true := by
  decide +kernel

theorem tot14053 : totK PD2M8K2 D2M8K2.t14053 = [0, 0, 98934374103, 342765362613, 353744325585, 71918152016, 1188254444, 0] := by
  decide +kernel

theorem rows14054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14054 = true := by
  decide +kernel

theorem tot14054 : totK PD2M8K2 D2M8K2.t14054 = [0, 0, 192283093851, 481100897617, 224996872357, 12157532660, 0, 0] := by
  decide +kernel

theorem rows14055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14055 = true := by
  decide +kernel

theorem tot14055 : totK PD2M8K2 D2M8K2.t14055 = [0, 0, 88260735693, 427509053927, 338902662916, 28910391748, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
