import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12888 = true := by
  decide +kernel

theorem tot12888 : totK PD2M8K2 D2M8K2.t12888 = [0, 85371767328, 339084264071, 379201271466, 85387928601, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12889 = true := by
  decide +kernel

theorem tot12889 : totK PD2M8K2 D2M8K2.t12889 = [0, 0, 329525972591, 506298544782, 65420911405, 0, 0, 0] := by
  decide +kernel

theorem rows12890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12890 = true := by
  decide +kernel

theorem tot12890 : totK PD2M8K2 D2M8K2.t12890 = [0, 192401929322, 449835803308, 242908970215, 27040590748, 0, 0, 0] := by
  decide +kernel

theorem rows12891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12891 = true := by
  decide +kernel

theorem tot12891 : totK PD2M8K2 D2M8K2.t12891 = [0, 179904121073, 471337268090, 228445080152, 12373752831, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
