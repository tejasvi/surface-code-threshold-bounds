import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4172 = true := by
  decide +kernel

theorem tot4172 : totK PA10K2 A10K2.t4172 = [0, 549783201733, 1861815558467, 1803230436443, 589508800830, 100724524850, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows4173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4173 = true := by
  decide +kernel

theorem tot4173 : totK PA10K2 A10K2.t4173 = [469390687660, 1524399419277, 1609071233202, 882440736865, 359004583317, 43920743672, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4174 = true := by
  decide +kernel

theorem tot4174 : totK PA10K2 A10K2.t4174 = [293593425400, 1529474980433, 2206766400502, 857287785954, 71852805742, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4175 = true := by
  decide +kernel

theorem tot4175 : totK PA10K2 A10K2.t4175 = [0, 489615580073, 1814844335652, 1941502981968, 517659121030, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
