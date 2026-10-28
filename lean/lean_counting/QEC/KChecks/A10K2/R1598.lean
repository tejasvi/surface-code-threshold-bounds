import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6392 = true := by
  decide +kernel

theorem tot6392 : totK PA10K2 A10K2.t6392 = [0, 0, 459831370100, 1809487593928, 1904339101090, 498428651644, 31690783744, 0, 0, 0] := by
  decide +kernel

theorem rows6393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6393 = true := by
  decide +kernel

theorem tot6393 : totK PA10K2 A10K2.t6393 = [0, 0, 550643614431, 1828647890003, 1682060002314, 447705638507, 44205580057, 0, 0, 0] := by
  decide +kernel

theorem rows6394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6394 = true := by
  decide +kernel

theorem tot6394 : totK PA10K2 A10K2.t6394 = [0, 0, 300380387770, 1547135498337, 2065185963048, 647345960666, 38070154274, 0, 0, 0] := by
  decide +kernel

theorem rows6395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6395 = true := by
  decide +kernel

theorem tot6395 : totK PA10K2 A10K2.t6395 = [303494667383, 698722476234, 335342380442, 477810004925, 1413378277207, 1112407955340, 233448211815, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
