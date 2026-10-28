import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14432 = true := by
  decide +kernel

theorem tot14432 : totK PD2M8K2 D2M8K2.t14432 = [160188045679, 451082011887, 278798992871, 31473371772, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14433 = true := by
  decide +kernel

theorem tot14433 : totK PD2M8K2 D2M8K2.t14433 = [175926035156, 456263706919, 241938285076, 15093591344, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14434 = true := by
  decide +kernel

theorem tot14434 : totK PD2M8K2 D2M8K2.t14434 = [87346212865, 338221044405, 387574012799, 87276318236, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows14435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14435 = true := by
  decide +kernel

theorem tot14435 : totK PD2M8K2 D2M8K2.t14435 = [0, 215994165407, 477599719482, 168911202830, 9482920370, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
