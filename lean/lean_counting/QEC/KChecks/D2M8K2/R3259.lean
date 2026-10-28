import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13036 = true := by
  decide +kernel

theorem tot13036 : totK PD2M8K2 D2M8K2.t13036 = [0, 198503504971, 462884151774, 236728908965, 18405594348, 0, 0, 0] := by
  decide +kernel

theorem rows13037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13037 = true := by
  decide +kernel

theorem tot13037 : totK PD2M8K2 D2M8K2.t13037 = [0, 56283093014, 324546119070, 416074974479, 96876419879, 1268739303, 0, 0] := by
  decide +kernel

theorem rows13038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13038 = true := by
  decide +kernel

theorem tot13038 : totK PD2M8K2 D2M8K2.t13038 = [0, 0, 211625695065, 482373084375, 182470542691, 7442000727, 0, 0] := by
  decide +kernel

theorem rows13039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13039 = true := by
  decide +kernel

theorem tot13039 : totK PD2M8K2 D2M8K2.t13039 = [0, 0, 188664931526, 468942255852, 216171372831, 14707859566, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
