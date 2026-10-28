import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t392 = true := by
  decide +kernel

theorem tot392 : totK PA10K2 A10K2.t392 = [0, 0, 343797452195, 1500021580097, 2084112569732, 969212554279, 94109989764, 0, 0, 0] := by
  decide +kernel

theorem rows393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t393 = true := by
  decide +kernel

theorem tot393 : totK PA10K2 A10K2.t393 = [0, 0, 527544132743, 1898849763727, 1950524092268, 500441390178, 18225898793, 0, 0, 0] := by
  decide +kernel

theorem rows394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t394 = true := by
  decide +kernel

theorem tot394 : totK PA10K2 A10K2.t394 = [0, 0, 0, 689318669545, 2181779792341, 1765073887474, 288441925431, 6066958478, 0, 0] := by
  decide +kernel

theorem rows395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t395 = true := by
  decide +kernel

theorem tot395 : totK PA10K2 A10K2.t395 = [132922702514, 322593360771, 188003870903, 345071581739, 1378690207172, 1814854766966, 672670345159, 55043167628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
