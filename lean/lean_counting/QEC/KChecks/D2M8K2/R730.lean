import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2920 = true := by
  decide +kernel

theorem tot2920 : totK PD2M8K2 D2M8K2.t2920 = [0, 159123879406, 419606419479, 299506826332, 35525069403, 0, 0, 0] := by
  decide +kernel

theorem rows2921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2921 = true := by
  decide +kernel

theorem tot2921 : totK PD2M8K2 D2M8K2.t2921 = [0, 189406050724, 482345157454, 215090740884, 14600810888, 0, 0, 0] := by
  decide +kernel

theorem rows2922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2922 = true := by
  decide +kernel

theorem tot2922 : totK PD2M8K2 D2M8K2.t2922 = [0, 160909588824, 473316874690, 242524484317, 11046849895, 0, 0, 0] := by
  decide +kernel

theorem rows2923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2923 = true := by
  decide +kernel

theorem tot2923 : totK PD2M8K2 D2M8K2.t2923 = [0, 182728887381, 462280891019, 249316375959, 18246066036, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
