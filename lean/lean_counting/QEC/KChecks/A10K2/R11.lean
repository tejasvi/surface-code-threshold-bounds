import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows44 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t44 = true := by
  decide +kernel

theorem tot44 : totK PA10K2 A10K2.t44 = [0, 580762403263, 1816720600820, 1603288846328, 573585508596, 233903418755, 37310410385, 0, 0, 0] := by
  decide +kernel

theorem rows45 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t45 = true := by
  decide +kernel

theorem tot45 : totK PA10K2 A10K2.t45 = [0, 290724629903, 1508086241150, 2201401470458, 878693179802, 67727243258, 0, 0, 0, 0] := by
  decide +kernel

theorem rows46 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t46 = true := by
  decide +kernel

theorem tot46 : totK PA10K2 A10K2.t46 = [0, 0, 502416718132, 1821364830028, 1773884401455, 473925801065, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows47 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t47 = true := by
  decide +kernel

theorem tot47 : totK PA10K2 A10K2.t47 = [0, 440942156918, 1610458202064, 1957418584056, 806126286020, 75440906312, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
