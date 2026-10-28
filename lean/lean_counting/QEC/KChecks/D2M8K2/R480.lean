import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1920 = true := by
  decide +kernel

theorem tot1920 : totK PD2M8K2 D2M8K2.t1920 = [0, 23509793184, 310489707682, 463955538551, 100254535445, 1198073392, 0, 0] := by
  decide +kernel

theorem rows1921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1921 = true := by
  decide +kernel

theorem tot1921 : totK PD2M8K2 D2M8K2.t1921 = [0, 86455869629, 313361453653, 379095857564, 119535602468, 4257574148, 0, 0] := by
  decide +kernel

theorem rows1922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1922 = true := by
  decide +kernel

theorem tot1922 : totK PD2M8K2 D2M8K2.t1922 = [0, 176448034620, 463674428144, 254386568575, 22206430004, 0, 0, 0] := by
  decide +kernel

theorem rows1923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1923 = true := by
  decide +kernel

theorem tot1923 : totK PD2M8K2 D2M8K2.t1923 = [0, 177361382255, 465165945133, 251742292503, 17689192246, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
