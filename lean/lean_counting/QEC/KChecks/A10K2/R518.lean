import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2072 = true := by
  decide +kernel

theorem tot2072 : totK PA10K2 A10K2.t2072 = [0, 323255249417, 1585470885205, 2220918594367, 795093236917, 36915635290, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2073 = true := by
  decide +kernel

theorem tot2073 : totK PA10K2 A10K2.t2073 = [0, 0, 604050970927, 2007272680787, 1871603304488, 414502228601, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows2074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2074 = true := by
  decide +kernel

theorem tot2074 : totK PA10K2 A10K2.t2074 = [0, 321323071444, 1124073986064, 1557877557450, 1375056517979, 521195429593, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows2075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2075 = true := by
  decide +kernel

theorem tot2075 : totK PA10K2 A10K2.t2075 = [0, 507715120288, 1779153169776, 1912710329698, 545635607268, 32731286466, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
