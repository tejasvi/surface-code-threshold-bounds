import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13964 = true := by
  decide +kernel

theorem tot13964 : totK PD2M8K2 D2M8K2.t13964 = [0, 0, 223120178203, 484832676891, 164160749818, 6603055607, 0, 0] := by
  decide +kernel

theorem rows13965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13965 = true := by
  decide +kernel

theorem tot13965 : totK PD2M8K2 D2M8K2.t13965 = [0, 141137605987, 400349430317, 296353187896, 68892397268, 2221265353, 0, 0] := by
  decide +kernel

theorem rows13966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13966 = true := by
  decide +kernel

theorem tot13966 : totK PD2M8K2 D2M8K2.t13966 = [0, 170518909437, 447493864790, 256766200307, 18114779563, 0, 0, 0] := by
  decide +kernel

theorem rows13967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13967 = true := by
  decide +kernel

theorem tot13967 : totK PD2M8K2 D2M8K2.t13967 = [0, 90293707314, 370999791198, 362594642314, 60119190896, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
