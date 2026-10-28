import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6168 = true := by
  decide +kernel

theorem tot6168 : totK PD2M8K2 D2M8K2.t6168 = [195081751892, 458271032211, 230606974595, 16859277328, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6169 = true := by
  decide +kernel

theorem tot6169 : totK PD2M8K2 D2M8K2.t6169 = [22012745738, 334220047377, 448798121404, 87481053214, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows6170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6170 = true := by
  decide +kernel

theorem tot6170 : totK PD2M8K2 D2M8K2.t6170 = [56255723409, 288881088177, 430283200284, 115681445065, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows6171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6171 = true := by
  decide +kernel

theorem tot6171 : totK PD2M8K2 D2M8K2.t6171 = [185554704325, 468721493439, 253283481966, 23350948179, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
