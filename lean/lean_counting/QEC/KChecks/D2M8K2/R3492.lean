import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13968 = true := by
  decide +kernel

theorem tot13968 : totK PD2M8K2 D2M8K2.t13968 = [0, 0, 292739578849, 511666763605, 95829814341, 0, 0, 0] := by
  decide +kernel

theorem rows13969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13969 = true := by
  decide +kernel

theorem tot13969 : totK PD2M8K2 D2M8K2.t13969 = [0, 183205682383, 437529944515, 250707096696, 51735347653, 2498823382, 0, 0] := by
  decide +kernel

theorem rows13970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13970 = true := by
  decide +kernel

theorem tot13970 : totK PD2M8K2 D2M8K2.t13970 = [0, 186166860624, 462053626155, 236781990159, 15909660794, 0, 0, 0] := by
  decide +kernel

theorem rows13971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13971 = true := by
  decide +kernel

theorem tot13971 : totK PD2M8K2 D2M8K2.t13971 = [0, 56561114677, 342752265698, 431494128735, 79312869350, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
