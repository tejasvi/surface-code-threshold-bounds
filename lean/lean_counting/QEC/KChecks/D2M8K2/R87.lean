import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t348 = true := by
  decide +kernel

theorem tot348 : totK PD2M8K2 D2M8K2.t348 = [183116257439, 456337568171, 203172324530, 28795686501, 31645760018, 5679676912, 0, 0] := by
  decide +kernel

theorem rows349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t349 = true := by
  decide +kernel

theorem tot349 : totK PD2M8K2 D2M8K2.t349 = [202665045914, 464726337083, 204951500348, 12506970531, 0, 0, 0, 0] := by
  decide +kernel

theorem rows350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t350 = true := by
  decide +kernel

theorem tot350 : totK PD2M8K2 D2M8K2.t350 = [31922977063, 307242873170, 452100115842, 100333533838, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t351 = true := by
  decide +kernel

theorem tot351 : totK PD2M8K2 D2M8K2.t351 = [76288307161, 363892282770, 413177194443, 52974878443, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
