import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4660 = true := by
  decide +kernel

theorem tot4660 : totK PA10K2 A10K2.t4660 = [0, 557255197736, 1946851891769, 1952065225757, 510941928309, 26374032118, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4661 = true := by
  decide +kernel

theorem tot4661 : totK PA10K2 A10K2.t4661 = [0, 119627100822, 1105656287277, 2223544498337, 1356975894244, 186035632959, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4662 = true := by
  decide +kernel

theorem tot4662 : totK PA10K2 A10K2.t4662 = [0, 0, 377997415400, 1677522123245, 2080622522525, 722649649905, 47540011751, 0, 0, 0] := by
  decide +kernel

theorem rows4663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4663 = true := by
  decide +kernel

theorem tot4663 : totK PA10K2 A10K2.t4663 = [0, 0, 494266445023, 1909280201440, 1893865950674, 461000670862, 26479096260, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
