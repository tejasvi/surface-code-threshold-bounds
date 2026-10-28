import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1064 = true := by
  decide +kernel

theorem tot1064 : totK PA10K2 A10K2.t1064 = [0, 0, 848878887967, 2237384133626, 1635892090146, 295435032037, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows1065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1065 = true := by
  decide +kernel

theorem tot1065 : totK PA10K2 A10K2.t1065 = [0, 0, 434000568451, 1836731383231, 2187799899272, 663891357327, 24447301666, 0, 0, 0] := by
  decide +kernel

theorem rows1066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1066 = true := by
  decide +kernel

theorem tot1066 : totK PA10K2 A10K2.t1066 = [0, 0, 522280560115, 1847122477607, 1800847164342, 521402031336, 51676217198, 0, 0, 0] := by
  decide +kernel

theorem rows1067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1067 = true := by
  decide +kernel

theorem tot1067 : totK PA10K2 A10K2.t1067 = [0, 0, 297007965898, 1443379956237, 2167070418804, 933780500245, 73579494916, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
