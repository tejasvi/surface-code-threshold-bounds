import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3384 = true := by
  decide +kernel

theorem tot3384 : totK PD2M8K2 D2M8K2.t3384 = [0, 87698990320, 128166751894, 202264067111, 340151853765, 93603305476, 3819176523, 0] := by
  decide +kernel

theorem rows3385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3385 = true := by
  decide +kernel

theorem tot3385 : totK PD2M8K2 D2M8K2.t3385 = [0, 151064652885, 464861487238, 261213542242, 14007748576, 0, 0, 0] := by
  decide +kernel

theorem rows3386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3386 = true := by
  decide +kernel

theorem tot3386 : totK PD2M8K2 D2M8K2.t3386 = [0, 140073074235, 426894497788, 295973360723, 26517799009, 0, 0, 0] := by
  decide +kernel

theorem rows3387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3387 = true := by
  decide +kernel

theorem tot3387 : totK PD2M8K2 D2M8K2.t3387 = [0, 0, 276921748620, 508822575436, 103665232429, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
