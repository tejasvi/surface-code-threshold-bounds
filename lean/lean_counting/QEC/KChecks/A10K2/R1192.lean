import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4768 = true := by
  decide +kernel

theorem tot4768 : totK PA10K2 A10K2.t4768 = [0, 0, 0, 849888571957, 2366170468641, 1389611258879, 140828445783, 0, 0, 0] := by
  decide +kernel

theorem rows4769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4769 = true := by
  decide +kernel

theorem tot4769 : totK PA10K2 A10K2.t4769 = [0, 0, 480663153280, 1786619554626, 1865335492628, 592981495205, 91518344435, 5447185874, 0, 0] := by
  decide +kernel

theorem rows4770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4770 = true := by
  decide +kernel

theorem tot4770 : totK PA10K2 A10K2.t4770 = [0, 0, 296008817083, 1490070347407, 2158328747920, 750118487336, 44125575270, 0, 0, 0] := by
  decide +kernel

theorem rows4771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4771 = true := by
  decide +kernel

theorem tot4771 : totK PA10K2 A10K2.t4771 = [0, 0, 274997330428, 1115506320783, 1934221420990, 1156837795819, 180973809845, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
