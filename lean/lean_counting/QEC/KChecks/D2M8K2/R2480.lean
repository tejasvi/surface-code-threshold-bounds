import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9920 = true := by
  decide +kernel

theorem tot9920 : totK PD2M8K2 D2M8K2.t9920 = [0, 0, 171594259033, 454673627990, 264794498716, 26910248469, 0, 0] := by
  decide +kernel

theorem rows9921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9921 = true := by
  decide +kernel

theorem tot9921 : totK PD2M8K2 D2M8K2.t9921 = [0, 0, 172988275614, 453840211684, 252141376560, 16331368848, 0, 0] := by
  decide +kernel

theorem rows9922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9922 = true := by
  decide +kernel

theorem tot9922 : totK PD2M8K2 D2M8K2.t9922 = [0, 0, 93518571537, 346881309550, 374313122430, 76572545399, 1242138600, 0] := by
  decide +kernel

theorem rows9923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9923 = true := by
  decide +kernel

theorem tot9923 : totK PD2M8K2 D2M8K2.t9923 = [0, 0, 0, 302287811955, 474400238262, 108631218049, 3612612137, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
