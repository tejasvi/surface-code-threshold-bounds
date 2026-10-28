import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1932 = true := by
  decide +kernel

theorem tot1932 : totK PD2M8K2 D2M8K2.t1932 = [0, 0, 193482911268, 467283936501, 228970159306, 14672519909, 0, 0] := by
  decide +kernel

theorem rows1933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1933 = true := by
  decide +kernel

theorem tot1933 : totK PD2M8K2 D2M8K2.t1933 = [0, 0, 178658315962, 469903906727, 228133856704, 13291426806, 0, 0] := by
  decide +kernel

theorem rows1934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1934 = true := by
  decide +kernel

theorem tot1934 : totK PD2M8K2 D2M8K2.t1934 = [0, 0, 0, 305325114400, 485433591194, 84404615360, 1075657031, 0] := by
  decide +kernel

theorem rows1935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1935 = true := by
  decide +kernel

theorem tot1935 : totK PD2M8K2 D2M8K2.t1935 = [0, 0, 81861026506, 325443540790, 365863980088, 91956481873, 3804183361, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
