import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15780 = true := by
  decide +kernel

theorem tot15780 : totK PD2M8K2 D2M8K2.t15780 = [0, 0, 0, 202632800847, 491861854232, 184526602968, 7375673972, 0] := by
  decide +kernel

theorem rows15781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15781 = true := by
  decide +kernel

theorem tot15781 : totK PD2M8K2 D2M8K2.t15781 = [0, 173658224399, 390247151006, 135198232904, 77643436112, 99925118960, 13338039113, 0] := by
  decide +kernel

theorem rows15782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15782 = true := by
  decide +kernel

theorem tot15782 : totK PD2M8K2 D2M8K2.t15782 = [0, 171862900460, 453902274704, 239081579512, 17044607505, 0, 0, 0] := by
  decide +kernel

theorem rows15783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15783 = true := by
  decide +kernel

theorem tot15783 : totK PD2M8K2 D2M8K2.t15783 = [0, 87765346930, 342008833462, 382727787172, 85387928601, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
