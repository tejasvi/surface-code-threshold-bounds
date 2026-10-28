import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14224 = true := by
  decide +kernel

theorem tot14224 : totK PD2M8K2 D2M8K2.t14224 = [0, 89748608524, 360575429351, 342036817208, 52858600626, 1021600638, 0, 0] := by
  decide +kernel

theorem rows14225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14225 = true := by
  decide +kernel

theorem tot14225 : totK PD2M8K2 D2M8K2.t14225 = [0, 0, 281644593239, 463932909996, 100882605188, 1996768108, 0, 0] := by
  decide +kernel

theorem rows14226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14226 = true := by
  decide +kernel

theorem tot14226 : totK PD2M8K2 D2M8K2.t14226 = [0, 190065920095, 452007195912, 236379630931, 20804815251, 0, 0, 0] := by
  decide +kernel

theorem rows14227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14227 = true := by
  decide +kernel

theorem tot14227 : totK PD2M8K2 D2M8K2.t14227 = [0, 212819444123, 484660872870, 207637122054, 9886925493, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
