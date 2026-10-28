import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10296 = true := by
  decide +kernel

theorem tot10296 : totK PD2M8K2 D2M8K2.t10296 = [0, 0, 19168591844, 349703594524, 418945313356, 64833050430, 1053411165, 0] := by
  decide +kernel

theorem rows10297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10297 = true := by
  decide +kernel

theorem tot10297 : totK PD2M8K2 D2M8K2.t10297 = [0, 0, 84636411730, 306492033850, 372490397539, 94878909120, 3667207281, 0] := by
  decide +kernel

theorem rows10298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10298 = true := by
  decide +kernel

theorem tot10298 : totK PD2M8K2 D2M8K2.t10298 = [0, 0, 156062567105, 452492283641, 267455237061, 21668877008, 0, 0] := by
  decide +kernel

theorem rows10299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10299 = true := by
  decide +kernel

theorem tot10299 : totK PD2M8K2 D2M8K2.t10299 = [0, 0, 181529627328, 471404340246, 247620572567, 14131730622, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
