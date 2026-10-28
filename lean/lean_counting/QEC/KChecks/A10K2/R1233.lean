import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4932 = true := by
  decide +kernel

theorem tot4932 : totK PA10K2 A10K2.t4932 = [0, 490345024882, 1597946842828, 1658424814458, 786999797788, 320992734074, 43132710386, 0, 0, 0] := by
  decide +kernel

theorem rows4933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4933 = true := by
  decide +kernel

theorem tot4933 : totK PA10K2 A10K2.t4933 = [0, 355484445270, 1606064966400, 2050324626327, 713819895924, 55444344262, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4934 = true := by
  decide +kernel

theorem tot4934 : totK PA10K2 A10K2.t4934 = [0, 0, 461659104712, 1852769251401, 1875149291379, 449744788659, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows4935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4935 = true := by
  decide +kernel

theorem tot4935 : totK PA10K2 A10K2.t4935 = [0, 461866678616, 1690932198079, 1814097176488, 710848065848, 124000099233, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
