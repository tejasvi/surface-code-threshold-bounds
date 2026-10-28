import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6000 = true := by
  decide +kernel

theorem tot6000 : totK PD2M8K2 D2M8K2.t6000 = [0, 88183717169, 331691432244, 361855666335, 123891839508, 14782677892, 0, 0] := by
  decide +kernel

theorem rows6001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6001 = true := by
  decide +kernel

theorem tot6001 : totK PD2M8K2 D2M8K2.t6001 = [0, 0, 174968889911, 457991564508, 247173543900, 13460187817, 0, 0] := by
  decide +kernel

theorem rows6002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6002 = true := by
  decide +kernel

theorem tot6002 : totK PD2M8K2 D2M8K2.t6002 = [0, 47389074975, 220592524811, 429532544268, 194758427977, 8166240555, 0, 0] := by
  decide +kernel

theorem rows6003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6003 = true := by
  decide +kernel

theorem tot6003 : totK PD2M8K2 D2M8K2.t6003 = [0, 181734905431, 469004234542, 252137954509, 23167094600, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
