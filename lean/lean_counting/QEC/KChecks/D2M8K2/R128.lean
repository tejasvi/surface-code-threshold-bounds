import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t512 = true := by
  decide +kernel

theorem tot512 : totK PD2M8K2 D2M8K2.t512 = [0, 0, 262761439537, 492713601900, 149618606295, 8423393484, 0, 0] := by
  decide +kernel

theorem rows513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t513 = true := by
  decide +kernel

theorem tot513 : totK PD2M8K2 D2M8K2.t513 = [0, 121541691012, 345787115139, 326492779411, 84585834062, 3462014130, 0, 0] := by
  decide +kernel

theorem rows514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t514 = true := by
  decide +kernel

theorem tot514 : totK PD2M8K2 D2M8K2.t514 = [0, 166958040082, 437004304014, 268136188284, 29530202054, 0, 0, 0] := by
  decide +kernel

theorem rows515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t515 = true := by
  decide +kernel

theorem tot515 : totK PD2M8K2 D2M8K2.t515 = [0, 123460538387, 444258100903, 287218592705, 19260630854, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
