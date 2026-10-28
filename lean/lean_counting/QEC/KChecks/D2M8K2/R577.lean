import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2308 = true := by
  decide +kernel

theorem tot2308 : totK PD2M8K2 D2M8K2.t2308 = [0, 0, 224621752649, 487309412353, 173575814685, 6954140929, 0, 0] := by
  decide +kernel

theorem rows2309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2309 = true := by
  decide +kernel

theorem tot2309 : totK PD2M8K2 D2M8K2.t2309 = [0, 79435114951, 331940458478, 389556884886, 89117015550, 2525684142, 0, 0] := by
  decide +kernel

theorem rows2310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2310 = true := by
  decide +kernel

theorem tot2310 : totK PD2M8K2 D2M8K2.t2310 = [0, 168303335474, 440773850041, 276768912273, 30487149178, 0, 0, 0] := by
  decide +kernel

theorem rows2311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2311 = true := by
  decide +kernel

theorem tot2311 : totK PD2M8K2 D2M8K2.t2311 = [0, 156056651899, 453961229391, 276212015147, 22593582089, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
