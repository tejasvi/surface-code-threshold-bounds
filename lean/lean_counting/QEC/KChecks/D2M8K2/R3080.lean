import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12320 = true := by
  decide +kernel

theorem tot12320 : totK PD2M8K2 D2M8K2.t12320 = [173846469577, 440475758945, 270375511097, 30233657518, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12321 = true := by
  decide +kernel

theorem tot12321 : totK PD2M8K2 D2M8K2.t12321 = [120221079836, 440782196005, 310182183751, 23025953820, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12322 = true := by
  decide +kernel

theorem tot12322 : totK PD2M8K2 D2M8K2.t12322 = [0, 203275492168, 488787267353, 184339587245, 9587713104, 0, 0, 0] := by
  decide +kernel

theorem rows12323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12323 = true := by
  decide +kernel

theorem tot12323 : totK PD2M8K2 D2M8K2.t12323 = [84672624166, 330837319426, 364344422237, 94522732229, 3462014130, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
