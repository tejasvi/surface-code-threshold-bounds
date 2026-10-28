import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12208 = true := by
  decide +kernel

theorem tot12208 : totK PD2M8K2 D2M8K2.t12208 = [0, 202051655921, 487128974134, 179105251831, 10369431706, 0, 0, 0] := by
  decide +kernel

theorem rows12209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12209 = true := by
  decide +kernel

theorem tot12209 : totK PD2M8K2 D2M8K2.t12209 = [157178836392, 439929734191, 280304874914, 44912195179, 1503593968, 0, 0, 0] := by
  decide +kernel

theorem rows12210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12210 = true := by
  decide +kernel

theorem tot12210 : totK PD2M8K2 D2M8K2.t12210 = [177860025660, 449893501534, 255570220765, 18401906518, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12211 = true := by
  decide +kernel

theorem tot12211 : totK PD2M8K2 D2M8K2.t12211 = [78976767030, 351244471684, 382983628938, 82483463031, 1197396724, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
