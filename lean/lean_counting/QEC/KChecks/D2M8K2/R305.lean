import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1220 = true := by
  decide +kernel

theorem tot1220 : totK PD2M8K2 D2M8K2.t1220 = [159324830838, 454088914851, 272697312332, 18399079691, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1221 = true := by
  decide +kernel

theorem tot1221 : totK PD2M8K2 D2M8K2.t1221 = [87922896509, 347557750256, 386177289154, 84808788403, 1197396724, 0, 0, 0] := by
  decide +kernel

theorem rows1222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1222 = true := by
  decide +kernel

theorem tot1222 : totK PD2M8K2 D2M8K2.t1222 = [0, 204069933037, 471396979820, 190732978923, 12006692157, 0, 0, 0] := by
  decide +kernel

theorem rows1223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1223 = true := by
  decide +kernel

theorem tot1223 : totK PD2M8K2 D2M8K2.t1223 = [162238061422, 443972262555, 285778658420, 39407071922, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
