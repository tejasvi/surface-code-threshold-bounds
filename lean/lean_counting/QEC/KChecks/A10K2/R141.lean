import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t564 = true := by
  decide +kernel

theorem tot564 : totK PA10K2 A10K2.t564 = [0, 92573202314, 861585452565, 2090110051977, 1336086058143, 239904770714, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t565 = true := by
  decide +kernel

theorem tot565 : totK PA10K2 A10K2.t565 = [0, 479138724816, 1907355141450, 1915308275371, 458372211295, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t566 = true := by
  decide +kernel

theorem tot566 : totK PA10K2 A10K2.t566 = [0, 231659201055, 1226839527473, 2148849289078, 1130005935883, 105341621814, 0, 0, 0, 0] := by
  decide +kernel

theorem rows567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t567 = true := by
  decide +kernel

theorem tot567 : totK PA10K2 A10K2.t567 = [0, 63936775576, 585919588230, 1823368205799, 1759267204833, 463400746557, 30818366867, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
