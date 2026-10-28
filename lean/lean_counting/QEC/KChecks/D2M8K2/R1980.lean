import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7920 = true := by
  decide +kernel

theorem tot7920 : totK PD2M8K2 D2M8K2.t7920 = [0, 0, 195276851872, 482533519812, 190175644644, 11885407614, 0, 0] := by
  decide +kernel

theorem rows7921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7921 = true := by
  decide +kernel

theorem tot7921 : totK PD2M8K2 D2M8K2.t7921 = [0, 170049229353, 445480289785, 252350505385, 31481852181, 0, 0, 0] := by
  decide +kernel

theorem rows7922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7922 = true := by
  decide +kernel

theorem tot7922 : totK PD2M8K2 D2M8K2.t7922 = [0, 179552045913, 439215335588, 261721346946, 20681517972, 0, 0, 0] := by
  decide +kernel

theorem rows7923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7923 = true := by
  decide +kernel

theorem tot7923 : totK PD2M8K2 D2M8K2.t7923 = [0, 51519207145, 338202382249, 404692451446, 80901069045, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
