import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11908 = true := by
  decide +kernel

theorem tot11908 : totK PD2M8K2 D2M8K2.t11908 = [142936575108, 450988647241, 283511586641, 22017729826, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11909 = true := by
  decide +kernel

theorem tot11909 : totK PD2M8K2 D2M8K2.t11909 = [0, 293184231741, 520719838481, 100699065669, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows11910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11910 = true := by
  decide +kernel

theorem tot11910 : totK PD2M8K2 D2M8K2.t11910 = [142937165512, 369328160789, 300606437901, 93392001605, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows11911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11911 = true := by
  decide +kernel

theorem tot11911 : totK PD2M8K2 D2M8K2.t11911 = [153686016631, 440502158969, 292681652230, 28746415651, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
