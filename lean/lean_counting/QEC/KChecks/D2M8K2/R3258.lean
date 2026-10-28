import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13032 = true := by
  decide +kernel

theorem tot13032 : totK PD2M8K2 D2M8K2.t13032 = [0, 204923444032, 476287068984, 213538765233, 12356293777, 0, 0, 0] := by
  decide +kernel

theorem rows13033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13033 = true := by
  decide +kernel

theorem tot13033 : totK PD2M8K2 D2M8K2.t13033 = [0, 0, 296030311980, 493858400369, 100131597282, 1164319620, 0, 0] := by
  decide +kernel

theorem rows13034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13034 = true := by
  decide +kernel

theorem tot13034 : totK PD2M8K2 D2M8K2.t13034 = [0, 0, 205888008899, 471766759902, 189578754645, 11879463720, 0, 0] := by
  decide +kernel

theorem rows13035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13035 = true := by
  decide +kernel

theorem tot13035 : totK PD2M8K2 D2M8K2.t13035 = [0, 173197134760, 451982428114, 258044960681, 26997540542, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
