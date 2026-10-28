import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1616 = true := by
  decide +kernel

theorem tot1616 : totK PA10K2 A10K2.t1616 = [0, 0, 578058941085, 1886411928646, 1794656826444, 456635519719, 30953568651, 0, 0, 0] := by
  decide +kernel

theorem rows1617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1617 = true := by
  decide +kernel

theorem tot1617 : totK PA10K2 A10K2.t1617 = [0, 0, 0, 1063501079317, 2408631162756, 1044736807676, 97901981758, 0, 0, 0] := by
  decide +kernel

theorem rows1618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1618 = true := by
  decide +kernel

theorem tot1618 : totK PA10K2 A10K2.t1618 = [0, 0, 421249598066, 1380628695824, 1742253023101, 981240855513, 194362794041, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1619 = true := by
  decide +kernel

theorem tot1619 : totK PA10K2 A10K2.t1619 = [0, 0, 405404560339, 1744524341857, 2044085511361, 660625867874, 43030065704, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
