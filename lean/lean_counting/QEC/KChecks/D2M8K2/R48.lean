import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t192 = true := by
  decide +kernel

theorem tot192 : totK PD2M8K2 D2M8K2.t192 = [0, 144051062126, 448531195685, 293117634074, 23562781175, 0, 0, 0] := by
  decide +kernel

theorem rows193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t193 = true := by
  decide +kernel

theorem tot193 : totK PD2M8K2 D2M8K2.t193 = [0, 0, 210994260295, 500099921212, 158820262962, 4928554699, 0, 0] := by
  decide +kernel

theorem rows194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t194 = true := by
  decide +kernel

theorem tot194 : totK PD2M8K2 D2M8K2.t194 = [0, 0, 191277742901, 462617183456, 197710119945, 16843409175, 0, 0] := by
  decide +kernel

theorem rows195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t195 = true := by
  decide +kernel

theorem tot195 : totK PD2M8K2 D2M8K2.t195 = [0, 0, 205175542030, 479058765032, 192019357061, 9610913563, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
