import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t904 = true := by
  decide +kernel

theorem tot904 : totK PA10K2 A10K2.t904 = [0, 0, 521957965441, 1786574490336, 1791946802135, 589140950540, 62889663184, 0, 0, 0] := by
  decide +kernel

theorem rows905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t905 = true := by
  decide +kernel

theorem tot905 : totK PA10K2 A10K2.t905 = [0, 0, 296182446550, 1486500510051, 2192866277662, 879006669313, 60392598015, 0, 0, 0] := by
  decide +kernel

theorem rows906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t906 = true := by
  decide +kernel

theorem tot906 : totK PA10K2 A10K2.t906 = [0, 0, 278113035350, 1152566060494, 1854153479842, 1235890507312, 235498417031, 7007974415, 0, 0] := by
  decide +kernel

theorem rows907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t907 = true := by
  decide +kernel

theorem tot907 : totK PA10K2 A10K2.t907 = [0, 0, 488620151044, 1936421280755, 1981375899578, 396356437137, 11531959710, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
