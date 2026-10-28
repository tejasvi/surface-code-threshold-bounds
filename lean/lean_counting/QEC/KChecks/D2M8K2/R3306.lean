import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13224 = true := by
  decide +kernel

theorem tot13224 : totK PD2M8K2 D2M8K2.t13224 = [0, 156083584090, 436463504990, 278100727605, 34157472235, 0, 0, 0] := by
  decide +kernel

theorem rows13225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13225 = true := by
  decide +kernel

theorem tot13225 : totK PD2M8K2 D2M8K2.t13225 = [0, 181364961724, 459949460580, 239829454948, 14865664283, 0, 0, 0] := by
  decide +kernel

theorem rows13226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13226 = true := by
  decide +kernel

theorem tot13226 : totK PD2M8K2 D2M8K2.t13226 = [0, 73386097616, 320643154002, 393362440805, 90332778432, 1198073392, 0, 0] := by
  decide +kernel

theorem rows13227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13227 = true := by
  decide +kernel

theorem tot13227 : totK PD2M8K2 D2M8K2.t13227 = [0, 0, 200431604916, 485586059312, 178859882190, 9482920370, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
