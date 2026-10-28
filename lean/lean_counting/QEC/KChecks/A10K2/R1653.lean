import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6612 = true := by
  decide +kernel

theorem tot6612 : totK PA10K2 A10K2.t6612 = [0, 210763603685, 1208555479262, 2158435509655, 1276308924894, 196255958369, 15171143123, 0, 0, 0] := by
  decide +kernel

theorem rows6613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6613 = true := by
  decide +kernel

theorem tot6613 : totK PA10K2 A10K2.t6613 = [0, 77445172137, 636920581960, 1820979719265, 1741084985057, 420897998443, 16597605730, 0, 0, 0] := by
  decide +kernel

theorem rows6614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6614 = true := by
  decide +kernel

theorem tot6614 : totK PA10K2 A10K2.t6614 = [0, 445315634617, 1779383134704, 1952661084547, 513071396077, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6615 = true := by
  decide +kernel

theorem tot6615 : totK PA10K2 A10K2.t6615 = [0, 206529632795, 1076286805299, 1998690206472, 1287614425234, 196772798838, 5982052406, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
