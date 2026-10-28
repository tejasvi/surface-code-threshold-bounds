import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t656 = true := by
  decide +kernel

theorem tot656 : totK PD2M8K2 D2M8K2.t656 = [196165462438, 449891063354, 245736905079, 24251779029, 0, 0, 0, 0] := by
  decide +kernel

theorem rows657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t657 = true := by
  decide +kernel

theorem tot657 : totK PD2M8K2 D2M8K2.t657 = [190478287335, 472203667485, 222630857314, 12432084775, 0, 0, 0, 0] := by
  decide +kernel

theorem rows658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t658 = true := by
  decide +kernel

theorem tot658 : totK PD2M8K2 D2M8K2.t658 = [0, 241566596041, 437775509010, 198073368200, 21260150644, 0, 0, 0] := by
  decide +kernel

theorem rows659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t659 = true := by
  decide +kernel

theorem tot659 : totK PD2M8K2 D2M8K2.t659 = [0, 177905777066, 482800838429, 220428344437, 6542401075, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
